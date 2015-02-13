// Copyright 2014 <chaishushan{AT}gmail.com>. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// +build ingore

// QR codes encoder.
package main

import (
	//"bytes"
	"fmt"
	"image"
	_ "image/jpeg"
	"image/png"
	//"io/ioutil"
	"log"
	"os"
	"reflect"
	"syscall"
	"time"
	"unsafe"

	"github.com/AllenDang/w32"
	"github.com/kdar/goquirc"
	"github.com/spf13/nitro"
)

var (
	moduser32       = syscall.NewLazyDLL("user32.dll")
	procFindWindowW = moduser32.NewProc("FindWindowW")
)

func main() {
	hwnd, err := FindWindow("GxWindowClass", "World of Warcraft")
	if err != nil {
		log.Fatal(err)
	}

	ss_, err := CaptureRect(hwnd, image.Rect(0, 0, 160, 160))
	if err != nil {
		log.Fatal(err)
	}

	fp, err := os.Create("./out.png")
	if err != nil {
		log.Fatal(err)
	}
	defer fp.Close()

	png.Encode(fp, ss_)

	decoder := goquirc.New()
	defer decoder.Destroy()

	timer := nitro.Initialize()
	nitro.AnalysisOn = true
	for {
		timer.Step("starting")
		ss, err := CaptureRect(hwnd, image.Rect(0, 0, 160, 160))
		if err != nil {
			log.Fatal(err)
		}
		timer.Step("capture window")

		// buf := &bytes.Buffer{}
		// png.Encode(buf, ss)
		// pipeline := []pipe.Pipe{
		// 	pipe.Read(buf),
		// 	pipe.Exec("bin/zbarimg", "--raw", "-q", "PNG:-"),
		// }
		// p := pipe.Line(pipeline...)
		// output, stderr, err := pipe.DividedOutput(p)
		// if err != nil {
		// 	log.Fatal(err, string(stderr))
		// }
		// fmt.Println(string(output))

		text, _ := decoder.DecodeBytes(ss)
		fmt.Println(string(text))

		timer.Step("decode")

		time.Sleep(5 * time.Second)
	}
}

func FindWindow(cls string, win string) (ret w32.HWND, err error) {
	lpszClass := syscall.StringToUTF16Ptr(cls)
	lpszWindow := syscall.StringToUTF16Ptr(win)

	r0, _, e1 := syscall.Syscall(procFindWindowW.Addr(), 2, uintptr(unsafe.Pointer(lpszClass)), uintptr(unsafe.Pointer(lpszWindow)), 0)
	ret = w32.HWND(r0)
	if ret == 0 {
		if e1 != 0 {
			err = error(e1)
		} else {
			err = syscall.EINVAL
		}
	}
	return
}

func ScreenRect() (image.Rectangle, error) {
	hDC := w32.GetDC(0)
	if hDC == 0 {
		return image.Rectangle{}, fmt.Errorf("Could not Get primary display err:%d\n", w32.GetLastError())
	}
	defer w32.ReleaseDC(0, hDC)
	x := w32.GetDeviceCaps(hDC, w32.HORZRES)
	y := w32.GetDeviceCaps(hDC, w32.VERTRES)
	return image.Rect(0, 0, x, y), nil
}

func CaptureScreen() (*image.RGBA, error) {
	r, e := ScreenRect()
	if e != nil {
		return nil, e
	}
	return CaptureRect(0, r)
}

func CaptureWindow(hwnd w32.HWND) (*image.RGBA, error) {
	r, e := ScreenRect()
	if e != nil {
		return nil, e
	}
	return CaptureRect(hwnd, r)
}

func CaptureRect(hwnd w32.HWND, rect image.Rectangle) (*image.RGBA, error) {
	hDC := w32.GetDC(hwnd)
	if hDC == 0 {
		return nil, fmt.Errorf("Could not Get primary display err:%d.\n", w32.GetLastError())
	}
	defer w32.ReleaseDC(hwnd, hDC)

	m_hDC := w32.CreateCompatibleDC(hDC)
	if m_hDC == 0 {
		return nil, fmt.Errorf("Could not Create Compatible DC err:%d.\n", w32.GetLastError())
	}
	defer w32.DeleteDC(m_hDC)

	x, y := rect.Dx(), rect.Dy()

	bt := w32.BITMAPINFO{}
	bt.BmiHeader.BiSize = uint32(reflect.TypeOf(bt.BmiHeader).Size())
	bt.BmiHeader.BiWidth = int32(x)
	bt.BmiHeader.BiHeight = int32(-y)
	bt.BmiHeader.BiPlanes = 1
	bt.BmiHeader.BiBitCount = 32
	bt.BmiHeader.BiCompression = w32.BI_RGB

	ptr := unsafe.Pointer(uintptr(0))

	m_hBmp := w32.CreateDIBSection(m_hDC, &bt, w32.DIB_RGB_COLORS, &ptr, 0, 0)
	if m_hBmp == 0 {
		return nil, fmt.Errorf("Could not Create DIB Section err:%d.\n", w32.GetLastError())
	}
	if m_hBmp == w32.InvalidParameter {
		return nil, fmt.Errorf("One or more of the input parameters is invalid while calling CreateDIBSection.\n")
	}
	defer w32.DeleteObject(w32.HGDIOBJ(m_hBmp))

	obj := w32.SelectObject(m_hDC, w32.HGDIOBJ(m_hBmp))
	if obj == 0 {
		return nil, fmt.Errorf("error occurred and the selected object is not a region err:%d.\n", w32.GetLastError())
	}
	if obj == 0xffffffff { //GDI_ERROR
		return nil, fmt.Errorf("GDI_ERROR while calling SelectObject err:%d.\n", w32.GetLastError())
	}
	defer w32.DeleteObject(obj)

	//Note:BitBlt contains bad error handling, we will just assume it works and if it doesn't it will panic :x
	w32.BitBlt(m_hDC, 0, 0, x, y, hDC, rect.Min.X, rect.Min.Y, w32.SRCCOPY)

	var slice []byte
	hdrp := (*reflect.SliceHeader)(unsafe.Pointer(&slice))
	hdrp.Data = uintptr(ptr)
	hdrp.Len = x * y * 4
	hdrp.Cap = x * y * 4

	imageBytes := make([]byte, len(slice))

	for i := 0; i < len(imageBytes); i += 4 {
		imageBytes[i], imageBytes[i+2], imageBytes[i+1], imageBytes[i+3] = slice[i+2], slice[i], slice[i+1], slice[i+3]
	}

	img := &image.RGBA{imageBytes, 4 * x, image.Rect(0, 0, x, y)}
	return img, nil
}
